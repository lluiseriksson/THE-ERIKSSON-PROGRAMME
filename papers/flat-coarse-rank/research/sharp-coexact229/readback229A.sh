#!/bin/sh
export GOOGLE_APPLICATION_CREDENTIALS=/mnt/c/Users/lluis/AppData/Roaming/gcloud/application_default_credentials.json
/home/lluis/.local/bin/colab --auth adc --config /home/lluis/.config/colab-cli/tep229-a-sessions.json sessions > /mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-229/runtime229A-backend-readback.txt 2>&1
v=$?
printf '%s\n' "$v" > /mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-229/runtime229A-backend-readback.exit.tmp
mv /mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-229/runtime229A-backend-readback.exit.tmp /mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-229/runtime229A-backend-readback.exit
cat /mnt/d/Datos/the-eriksson-programme/autonomia/evidencia-229/runtime229A-backend-readback.txt
exit "$v"


