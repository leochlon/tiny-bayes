import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block189_checked : centerBlock 189 = true := by decide +kernel
#print axioms block189_checked
end PythiaCert.Output
