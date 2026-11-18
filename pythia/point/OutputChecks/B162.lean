import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block162_checked : centerBlock 162 = true := by decide +kernel
#print axioms block162_checked
end PythiaCert.Output
