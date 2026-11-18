import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block152_checked : centerBlock 152 = true := by decide +kernel
#print axioms block152_checked
end PythiaCert.Output
