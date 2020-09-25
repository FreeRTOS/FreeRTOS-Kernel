#!/bin/bash -

PROJECT=$1
echo "Verifying url links of: ${PROJECT}"
if [ ! -d "$PROJECT" ]
then
    echo "Directory passed does not exist"
    exit 2
fi

SCRIPT_RET=0

set -o nounset        # Treat unset variables as an error

declare -A dict

function test {
    while IFS= read -r LINE; do
        FILE=$(echo $LINE | cut -f 1 -d ':')
        URL=$(echo $LINE | grep -IoE '\b(https?|ftp|file)://[-A-Za-z0-9+&@#/%?=~_|!:,.;]*[-A-Za-z0-9+&@#/%=~_|]')

        # remove trailing / if it exists curl diferenciate between links with
        # and without / at the end
        # URL=`echo "$URL" | sed 's,/$,,'`
        dict+=(["$URL"]="$FILE ")
    done < <(grep -e 'https\?://' ${PROJECT} -RIa --exclude='*.exe' --exclude-dir=.git | tr '*' ' ')

    for UNIQ_URL in ${!dict[@]} # loop urls
    do
     CURL_RES=$(curl -I ${UNIQ_URL} 2>/dev/null| head -n 1 | cut -f 2 -d ' ')
     RES=$?

        if [ "${CURL_RES}" == '' -o "${CURL_RES}" != '200' ]
        then
            echo "URL is: ${UNIQ_URL}"
            echo "File names: ${dict[$UNIQ_URL]}"
            if [ "${CURL_RES}" == '' ]  # curl returned an error
            then
                CURL_RES=$RES
                SCRIPT_RET=1
            elif [ "${CURL_RES}" == '403' ]
            then
                SCRIPT_RET=1
            fi
            echo Result is: "${CURL_RES}"
            echo "================================="
        fi
    done

    if [ "${SCRIPT_RET}" -eq 0 ]
    then
        exit 0
    else
        exit 1
    fi
}

test

