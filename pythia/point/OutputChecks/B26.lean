import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block26_checked : centerBlock 26 = true := by decide +kernel
#print axioms block26_checked
end PythiaCert.Output
