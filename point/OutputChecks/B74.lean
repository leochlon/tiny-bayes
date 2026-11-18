import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block74_checked : centerBlock 74 = true := by decide +kernel
#print axioms block74_checked
end PythiaCert.Output
