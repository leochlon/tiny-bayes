import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block118_checked : centerBlock 118 = true := by decide +kernel
#print axioms block118_checked
end PythiaCert.Output
