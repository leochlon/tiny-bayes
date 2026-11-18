import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block194_checked : centerBlock 194 = true := by decide +kernel
#print axioms block194_checked
end PythiaCert.Output
