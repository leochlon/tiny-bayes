import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block121_checked : centerBlock 121 = true := by decide +kernel
#print axioms block121_checked
end PythiaCert.Output
