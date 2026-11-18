import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block116_checked : centerBlock 116 = true := by decide +kernel
#print axioms block116_checked
end PythiaCert.Output
