import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block70_checked : centerBlock 70 = true := by decide +kernel
#print axioms block70_checked
end PythiaCert.Output
