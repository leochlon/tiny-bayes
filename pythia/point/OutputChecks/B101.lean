import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block101_checked : centerBlock 101 = true := by decide +kernel
#print axioms block101_checked
end PythiaCert.Output
