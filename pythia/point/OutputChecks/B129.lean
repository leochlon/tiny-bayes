import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block129_checked : centerBlock 129 = true := by decide +kernel
#print axioms block129_checked
end PythiaCert.Output
