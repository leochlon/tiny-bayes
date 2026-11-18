import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block166_checked : centerBlock 166 = true := by decide +kernel
#print axioms block166_checked
end PythiaCert.Output
