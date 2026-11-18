import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block188_checked : centerBlock 188 = true := by decide +kernel
#print axioms block188_checked
end PythiaCert.Output
