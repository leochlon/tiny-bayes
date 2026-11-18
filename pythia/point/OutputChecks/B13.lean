import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block13_checked : centerBlock 13 = true := by decide +kernel
#print axioms block13_checked
end PythiaCert.Output
