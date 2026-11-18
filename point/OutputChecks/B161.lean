import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block161_checked : centerBlock 161 = true := by decide +kernel
#print axioms block161_checked
end PythiaCert.Output
