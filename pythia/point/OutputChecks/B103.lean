import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block103_checked : centerBlock 103 = true := by decide +kernel
#print axioms block103_checked
end PythiaCert.Output
