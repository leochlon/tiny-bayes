import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block20_checked : centerBlock 20 = true := by decide +kernel
#print axioms block20_checked
end PythiaCert.Output
