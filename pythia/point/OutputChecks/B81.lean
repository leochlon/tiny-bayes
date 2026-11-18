import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block81_checked : centerBlock 81 = true := by decide +kernel
#print axioms block81_checked
end PythiaCert.Output
