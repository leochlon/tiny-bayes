import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block144_checked : centerBlock 144 = true := by decide +kernel
#print axioms block144_checked
end PythiaCert.Output
