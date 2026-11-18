import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block99_checked : centerBlock 99 = true := by decide +kernel
#print axioms block99_checked
end PythiaCert.Output
