import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block91_checked : centerBlock 91 = true := by decide +kernel
#print axioms block91_checked
end PythiaCert.Output
