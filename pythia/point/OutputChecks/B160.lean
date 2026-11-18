import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block160_checked : centerBlock 160 = true := by decide +kernel
#print axioms block160_checked
end PythiaCert.Output
