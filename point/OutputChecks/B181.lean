import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block181_checked : centerBlock 181 = true := by decide +kernel
#print axioms block181_checked
end PythiaCert.Output
