import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block12_checked : centerBlock 12 = true := by decide +kernel
#print axioms block12_checked
end PythiaCert.Output
