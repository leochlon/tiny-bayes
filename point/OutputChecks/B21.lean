import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block21_checked : centerBlock 21 = true := by decide +kernel
#print axioms block21_checked
end PythiaCert.Output
