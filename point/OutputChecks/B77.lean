import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block77_checked : centerBlock 77 = true := by decide +kernel
#print axioms block77_checked
end PythiaCert.Output
