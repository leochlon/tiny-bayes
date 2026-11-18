import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block6_checked : centerBlock 6 = true := by decide +kernel
#print axioms block6_checked
end PythiaCert.Output
