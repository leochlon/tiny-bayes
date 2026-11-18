import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block153_checked : centerBlock 153 = true := by decide +kernel
#print axioms block153_checked
end PythiaCert.Output
