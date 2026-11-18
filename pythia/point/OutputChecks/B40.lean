import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block40_checked : centerBlock 40 = true := by decide +kernel
#print axioms block40_checked
end PythiaCert.Output
