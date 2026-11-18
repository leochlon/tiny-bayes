import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block27_checked : centerBlock 27 = true := by decide +kernel
#print axioms block27_checked
end PythiaCert.Output
