import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block193_checked : centerBlock 193 = true := by decide +kernel
#print axioms block193_checked
end PythiaCert.Output
