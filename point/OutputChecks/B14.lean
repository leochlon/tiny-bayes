import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block14_checked : centerBlock 14 = true := by decide +kernel
#print axioms block14_checked
end PythiaCert.Output
