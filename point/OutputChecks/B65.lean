import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block65_checked : centerBlock 65 = true := by decide +kernel
#print axioms block65_checked
end PythiaCert.Output
