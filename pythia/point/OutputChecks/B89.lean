import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block89_checked : centerBlock 89 = true := by decide +kernel
#print axioms block89_checked
end PythiaCert.Output
