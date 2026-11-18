import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block15_checked : centerBlock 15 = true := by decide +kernel
#print axioms block15_checked
end PythiaCert.Output
