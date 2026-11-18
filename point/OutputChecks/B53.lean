import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block53_checked : centerBlock 53 = true := by decide +kernel
#print axioms block53_checked
end PythiaCert.Output
