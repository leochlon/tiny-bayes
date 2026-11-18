import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block79_checked : centerBlock 79 = true := by decide +kernel
#print axioms block79_checked
end PythiaCert.Output
