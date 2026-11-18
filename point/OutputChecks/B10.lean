import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block10_checked : centerBlock 10 = true := by decide +kernel
#print axioms block10_checked
end PythiaCert.Output
