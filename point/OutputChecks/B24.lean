import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block24_checked : centerBlock 24 = true := by decide +kernel
#print axioms block24_checked
end PythiaCert.Output
