import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block96_checked : centerBlock 96 = true := by decide +kernel
#print axioms block96_checked
end PythiaCert.Output
