import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block85_checked : centerBlock 85 = true := by decide +kernel
#print axioms block85_checked
end PythiaCert.Output
