import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block42_checked : centerBlock 42 = true := by decide +kernel
#print axioms block42_checked
end PythiaCert.Output
