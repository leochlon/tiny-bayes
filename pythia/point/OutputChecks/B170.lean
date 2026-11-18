import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block170_checked : centerBlock 170 = true := by decide +kernel
#print axioms block170_checked
end PythiaCert.Output
