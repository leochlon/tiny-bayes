import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block82_checked : centerBlock 82 = true := by decide +kernel
#print axioms block82_checked
end PythiaCert.Output
