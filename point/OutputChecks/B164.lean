import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block164_checked : centerBlock 164 = true := by decide +kernel
#print axioms block164_checked
end PythiaCert.Output
