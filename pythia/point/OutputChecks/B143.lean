import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block143_checked : centerBlock 143 = true := by decide +kernel
#print axioms block143_checked
end PythiaCert.Output
