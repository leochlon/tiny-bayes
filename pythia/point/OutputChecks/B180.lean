import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block180_checked : centerBlock 180 = true := by decide +kernel
#print axioms block180_checked
end PythiaCert.Output
