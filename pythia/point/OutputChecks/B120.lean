import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block120_checked : centerBlock 120 = true := by decide +kernel
#print axioms block120_checked
end PythiaCert.Output
