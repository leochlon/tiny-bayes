import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block45_checked : centerBlock 45 = true := by decide +kernel
#print axioms block45_checked
end PythiaCert.Output
