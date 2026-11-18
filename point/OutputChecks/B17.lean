import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block17_checked : centerBlock 17 = true := by decide +kernel
#print axioms block17_checked
end PythiaCert.Output
