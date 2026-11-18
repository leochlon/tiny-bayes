import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block7_checked : centerBlock 7 = true := by decide +kernel
#print axioms block7_checked
end PythiaCert.Output
