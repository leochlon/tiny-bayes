import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block110_checked : centerBlock 110 = true := by decide +kernel
#print axioms block110_checked
end PythiaCert.Output
