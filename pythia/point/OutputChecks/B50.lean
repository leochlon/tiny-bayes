import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block50_checked : centerBlock 50 = true := by decide +kernel
#print axioms block50_checked
end PythiaCert.Output
