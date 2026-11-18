import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block106_checked : centerBlock 106 = true := by decide +kernel
#print axioms block106_checked
end PythiaCert.Output
