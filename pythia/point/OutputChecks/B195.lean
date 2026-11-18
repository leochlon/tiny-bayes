import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block195_checked : centerBlock 195 = true := by decide +kernel
#print axioms block195_checked
end PythiaCert.Output
