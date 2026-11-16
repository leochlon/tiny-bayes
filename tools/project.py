#!/usr/bin/env python3
"""Build and check a multi-module Lean development.

  python3 project.py build <dir> <NS> [--jobs N] [--only MODULE]
      Builds every module under <dir>/<NS>/ (module <NS>.A.B is the file <dir>/<NS>/A/B.lean) in dependency
      order, at most N Lean processes at once. Incremental: a module is rebuilt when its .olean is missing or older
      than its source or than the .olean of a module it imports. Outputs go to <dir>/.build/. With --only, builds
      that module and the modules it imports.

  python3 project.py check <NS> <dir> <tag> [--jobs N]
      Copies the .lean files under <dir>/<NS>/ into a fresh workspace and rejects the development if
      any file contains a banned token, imports anything other than Mathlib and the development's own modules, or lacks
      `namespace <NS>`. Builds every module from scratch, then lists each theorem or lemma declared in
      <dir>/<NS>/Main.lean with its statement and the axioms it depends on. A theorem counts only if those axioms
      are within propext, Classical.choice, Quot.sound. Prints JSON.

Needs LEAN_BIN (the lean executable) and LEAN_BASE_PATH (LEAN_PATH of a built Mathlib) in the environment.
"""
import json, os, re, shutil, subprocess, sys, time

BANNED = ["sorry", "admit", "axiom", "macro", "macro_rules", "syntax", "elab", "elab_rules", "declare_syntax_cat",
          "notation", "infix", "infixl", "infixr", "prefix", "postfix", "initialize", "builtin_initialize",
          "implemented_by", "extern", "unsafe", "native_decide", "ofReduceBool", "reduceBool", "run_cmd", "run_elab",
          "run_meta", "run_tac", "by_elab", "set_option debug", "import Lean", "prelude", "#eval", "#exit", "IO.",
          "System.", "+native"]
BANNED_RE = [r"@\[\s*init\b"]
OK_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SIDES = ("PRO", "CON", "CE")
LEAN_BIN = os.environ.get("LEAN_BIN", "lean")
BASE = os.environ.get("LEAN_BASE_PATH", "")


def banned_hits(text):
    hits = []
    for b in BANNED:
        tail = "" if b.endswith(".") else r"(?![A-Za-z0-9_])"
        if re.search(r"(?<![A-Za-z0-9_.])" + re.escape(b) + tail, text):
            hits.append(b)
    hits += [r for r in BANNED_RE if re.search(r, text)]
    return hits


def imports_of(text):
    return [m for line in re.findall(r"^\s*import\s+(.+)$", text, re.M) for m in line.split()]


def scan(root, side):
    """Module name -> (path, imports) for every .lean file under root/side/."""
    mods = {}
    top = os.path.join(root, side)
    for dp, dn, fn in os.walk(top):
        dn[:] = sorted(d for d in dn if not d.startswith("."))
        for f in sorted(fn):
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, root)[:-5]
                if not re.fullmatch(r"[A-Za-z0-9_/]+", rel):
                    raise SystemExit(f"bad module path {rel!r}: use letters, digits and _ only")
                mods[rel.replace(os.sep, ".")] = (p, imports_of(open(p, encoding="utf-8").read()))
    return mods


def olean(outdir, m):
    return os.path.join(outdir, *m.split(".")) + ".olean"


def closure(mods, targets):
    seen, stack = set(), list(targets)
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        stack += [d for d in mods[m][1] if d in mods]
    return seen


def build(root, mods, outdir, jobs, targets, incremental, timeout, log_dir, echo=True):
    """Compile modules in dependency order, at most `jobs` at once. Returns {module: {status, seconds, tail}}."""
    os.makedirs(outdir, exist_ok=True); os.makedirs(log_dir, exist_ok=True)
    deps = {m: [d for d in mods[m][1] if d in mods] for m in targets}
    env = dict(os.environ, LEAN_PATH=(BASE + ":" if BASE else "") + outdir)
    pending, running, res = set(targets), {}, {}

    def up_to_date(m):
        o = olean(outdir, m)
        if not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(mods[m][0]):
            return False
        return all(os.path.exists(olean(outdir, d)) and os.path.getmtime(olean(outdir, d)) <= os.path.getmtime(o)
                   for d in deps[m])

    while pending or running:
        progressed = True
        while progressed and len(running) < jobs:
            progressed = False
            for m in sorted(pending):
                if any(res.get(d, {}).get("status") in ("FAIL", "SKIP") for d in deps[m]):
                    pending.discard(m); res[m] = {"status": "SKIP", "seconds": 0, "tail": "an import failed"}
                    progressed = True; break
                if all(res.get(d, {}).get("status") in ("OK", "CACHED") for d in deps[m]):
                    pending.discard(m); progressed = True
                    if incremental and up_to_date(m):
                        res[m] = {"status": "CACHED", "seconds": 0, "tail": ""}
                        break
                    o = olean(outdir, m); os.makedirs(os.path.dirname(o), exist_ok=True)
                    lf = open(os.path.join(log_dir, m + ".log"), "w")
                    p = subprocess.Popen([LEAN_BIN, "-o", o, "-i", o[:-6] + ".ilean", mods[m][0]], cwd=root, env=env,
                                         stdout=lf, stderr=subprocess.STDOUT)
                    running[m] = (p, time.time(), lf)
                    break
        if not running:
            if pending:  # unresolvable: missing or cyclic imports
                for m in sorted(pending):
                    res[m] = {"status": "SKIP", "seconds": 0, "tail": "cyclic or unbuildable imports"}
                pending.clear()
            break
        time.sleep(0.3)
        for m, (p, t0, lf) in list(running.items()):
            rc = p.poll()
            if rc is None and time.time() - t0 > timeout:
                p.kill(); p.wait(); rc = "timeout"
            if rc is None:
                continue
            lf.close(); del running[m]
            sec = round(time.time() - t0, 1)
            out = open(os.path.join(log_dir, m + ".log"), encoding="utf-8", errors="replace").read()
            ok = rc == 0 and not re.search(r"(^|\n)[^\n]*:\d+:\d+: error", out)
            res[m] = {"status": "OK" if ok else "FAIL", "seconds": sec,
                      "tail": "" if ok else (f"exit {rc}\n" + out[-6000:])}
            if echo:
                print(f"{res[m]['status']:5} {m}  {sec}s", flush=True)
                if not ok:
                    print(res[m]["tail"][-3000:], flush=True)
    return res


def cmd_build(argv):
    d, side = argv[0], argv[1]
    jobs = int(argv[argv.index("--jobs") + 1]) if "--jobs" in argv else 24
    only = argv[argv.index("--only") + 1] if "--only" in argv else None
    if side not in SIDES:
        raise SystemExit("namespace must be PRO, CON or CE")
    root = os.path.abspath(d)
    mods = scan(root, side)
    if not mods:
        raise SystemExit(f"no modules under {d}/{side}/")
    targets = closure(mods, [only]) if only else set(mods)
    if only and only not in mods:
        raise SystemExit(f"unknown module {only}")
    for m in sorted(targets):
        missing = [i for i in mods[m][1] if i.startswith(side + ".") and i not in mods]
        if missing:
            print(f"note: {m} imports missing modules {missing}")
    t0 = time.time()
    res = build(root, mods, os.path.join(root, ".build"), max(1, jobs), targets, True, 6 * 3600, os.path.join(root, ".build", "_logs"))
    n = {s: sum(r["status"] == s for r in res.values()) for s in ("OK", "CACHED", "FAIL", "SKIP")}
    print(f"built {len(targets)} modules in {round(time.time() - t0, 1)}s with up to {jobs} at once: {n}")
    sys.exit(0 if not n["FAIL"] and not n["SKIP"] else 1)


def axioms_report(side, ws, outdir, names):
    q = [n if n.startswith(side + ".") else f"{side}.{n}" for n in names]
    src = f"import {side}.Main\nset_option pp.fullNames true\n" + "".join(
        f'#print "@@THM {i}"\n#check @{n}\n#print axioms {n}\n' for i, n in enumerate(q))
    env = dict(os.environ, LEAN_PATH=(BASE + ":" if BASE else "") + outdir)
    r = subprocess.run([LEAN_BIN, "--stdin"], input=src, cwd=ws, env=env, capture_output=True, text=True, timeout=3600)
    parts = re.split(r"@@THM (\d+)\n", r.stdout + r.stderr)
    seg = {int(parts[i]): parts[i + 1] for i in range(1, len(parts) - 1, 2)}
    res = {}
    for i, n in enumerate(q):
        log = seg.get(i, "")
        ax = re.search(r"depends on axioms: \[(.*?)\]", log, re.S)
        axs = sorted({x.strip() for x in ax.group(1).split(",")}) if ax else []
        found = "error" not in log.split("depends on axioms")[0].lower() and (ax is not None or "does not depend on any axioms" in log)
        res[n] = {"accepted": found and set(axs) <= OK_AXIOMS, "axioms": axs,
                  "statement": log.split("depends on axioms")[0].split("does not depend")[0].strip()[-3000:]}
    return res


def cmd_check(argv):
    side, d, tag = argv[0], argv[1], argv[2]
    jobs = int(argv[argv.index("--jobs") + 1]) if "--jobs" in argv else 24
    if side not in SIDES or not re.fullmatch(r"[A-Za-z0-9_-]{1,40}", tag):
        raise SystemExit("usage: check PRO|CON|CE <dir> <tag of letters, digits, _ or ->")
    src_root = os.path.abspath(d)
    here = os.getcwd()
    ws = os.path.join(here, "_check", f"{side}_{tag}")
    assert os.path.commonpath([here, ws]) == here
    if os.path.exists(ws):
        shutil.rmtree(ws)
    v = {"compiled": False}
    try:
        mods_src = scan(src_root, side)
    except SystemExit as e:
        v["reason"] = str(e); print(json.dumps(v, indent=1)); return
    if f"{side}.Main" not in mods_src:
        v["reason"] = f"no {d}/{side}/Main.lean"; print(json.dumps(v, indent=1)); return
    for m, (p, imps) in mods_src.items():
        text = open(p, encoding="utf-8").read()
        hits = banned_hits(text)
        bad = [i for i in imps if not (i == "Mathlib" or i.startswith("Mathlib.") or i in mods_src)]
        if hits:
            v["reason"] = f"banned tokens in {m}: {hits}"
        elif bad:
            v["reason"] = f"{m} imports {bad}: only Mathlib and the development's own modules are allowed"
        elif not re.search(rf"^\s*namespace\s+{side}\b", text, re.M):
            v["reason"] = f"{m}: everything must be inside namespace {side}"
        if "reason" in v:
            print(json.dumps(v, indent=1)); return
        dst = os.path.join(ws, os.path.relpath(p, src_root))
        os.makedirs(os.path.dirname(dst), exist_ok=True); shutil.copyfile(p, dst)
    mods = scan(ws, side)
    outdir = os.path.join(ws, ".build")
    t0 = time.time()
    res = build(ws, mods, outdir, max(1, jobs), set(mods), False, 6 * 3600, os.path.join(ws, "_logs"), echo=False)
    v["modules"] = len(mods); v["jobs"] = jobs; v["build_seconds"] = round(time.time() - t0, 1)
    v["slowest_modules"] = dict(sorted(((m, r["seconds"]) for m, r in res.items()), key=lambda x: -x[1])[:15])
    failed = {m: r for m, r in res.items() if r["status"] != "OK"}
    if failed:
        m = sorted(failed, key=lambda k: failed[k]["status"] != "FAIL")[0]
        v["reason"] = f"module {m} did not build ({failed[m]['status']})"; v["lean_output"] = failed[m]["tail"]
        print(json.dumps(v, indent=1, ensure_ascii=False)); return
    main_text = open(mods[f"{side}.Main"][0], encoding="utf-8").read()
    names = re.findall(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+)?(?:theorem|lemma)\s+([^\s:(\[{]+)", main_text, re.M)
    v["compiled"] = True
    v["theorems"] = axioms_report(side, ws, outdir, names)
    print(json.dumps(v, indent=1, ensure_ascii=False))


if __name__ == "__main__":
    if len(sys.argv) < 2 or sys.argv[1] not in ("build", "check"):
        raise SystemExit(__doc__)
    (cmd_build if sys.argv[1] == "build" else cmd_check)(sys.argv[2:])
