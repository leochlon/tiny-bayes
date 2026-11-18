import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block83_checked : centerBlock 83 = true := by decide +kernel
#print axioms block83_checked
end PythiaCert.Output
