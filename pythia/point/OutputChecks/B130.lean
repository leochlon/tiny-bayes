import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block130_checked : centerBlock 130 = true := by decide +kernel
#print axioms block130_checked
end PythiaCert.Output
