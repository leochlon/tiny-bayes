import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block104_checked : centerBlock 104 = true := by decide +kernel
#print axioms block104_checked
end PythiaCert.Output
